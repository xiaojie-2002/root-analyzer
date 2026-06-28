#!/usr/bin/env python3
# -*- coding: utf-8 -*-
# RootVision - 核心分析引擎

import os
import json
import csv
import gc
import math
import itertools
import colorsys
import traceback
import warnings
from datetime import datetime

import numpy as np
import cv2
from PIL import Image, ImageDraw, ImageFont
from skimage import morphology, measure
import psutil

import matplotlib.pyplot as plt


class RootSystemAnalyzer:
    """根系分析器核心类"""

    # 默认根系直径分级标准 (name, min_mm, max_mm)
    DEFAULT_DIAMETER_CLASSES = [
        ('超细根', 0.0, 0.5),
        ('细根',   0.5, 1.0),
        ('中根',   1.0, 2.0),
        ('粗根',   2.0, 5.0),
        ('超粗根', 5.0, float('inf')),
    ]

    def __init__(self, pixel_to_mm=0.1):
        self.pixel_to_mm = pixel_to_mm
        self.results = {}
        self.analysis_history = []
        self.scale_bar_length_mm = 10  # 默认比例尺长度(mm)
        self.scale_bar_position = (50, 50)  # 比例尺位置

        # 简化：只保存计数相关数据
        self.root_count = 0
        self.connected_components = []  # 连通组件信息

        # 添加根系参数
        self.root_parameters = {
            'total_length': 0.0,  # 总根长(mm)
            'total_area': 0.0,  # 总根系面积(mm²)
            'total_volume': 0.0,  # 总根体积(mm³)
            'total_surface': 0.0,  # 总根表面积(mm²)
            'specific_root_length': 0.0,  # 比根长(mm/mm²)
            'avg_diameter': 0.0,  # 平均根直径(mm)
            'diameter_distribution': {}  # 直径分布
        }

        # 过滤统计信息
        self.filter_stats = {
            'total_regions': 0,
            'filtered_regions': 0,
            'removed_regions': 0,
            'removal_percentage': 0.0
        }

        # 扫描图像专用参数
        self.scan_params = {
            'is_scanned': False,  # 是否为扫描图像
            'background_type': 'light',  # 背景类型：light/dark
            'scan_quality': 'high',  # 扫描质量：high/medium/low
            'resolution_dpi': 300,  # 扫描分辨率
        }

        # 扫描图像优化标志
        self.use_scan_optimization = False

        # 图像增强方法
        self.enhance_method = 'adaptive'  # 默认自适应增强

        # 扫描图像增强标志
        self.scan_enhanced = None

        # ROI区域（图像坐标），None表示全图分析
        self.roi_active = None

        # 自定义直径分级，None=使用DEFAULT_DIAMETER_CLASSES
        self.diameter_classes = None

    def _get_diameter_classes(self):
        """返回有效直径分级列表 [(name, min_mm, max_mm), ...]"""
        if self.diameter_classes and len(self.diameter_classes) >= 2:
            return self.diameter_classes
        return list(self.DEFAULT_DIAMETER_CLASSES)

    def _get_class_suffix_keys(self, class_name):
        """为给定分级名生成 results dict 键名"""
        return {
            'count': f'{class_name}数量',
            'volume': f'{class_name}体积(mm³)',
            'volume_pct': f'{class_name}体积占比(%)',
            'avg_diam': f'{class_name}平均直径(mm)',
        }

    def load_image(self, image_path):
        """加载图像"""
        try:
            self.original_image = cv2.imread(image_path)
            if self.original_image is None:
                raise ValueError(f"无法读取图像: {image_path}")

            self.image_path = image_path
            self.image_name = os.path.basename(image_path)

            # 获取图像尺寸
            self.image_height, self.image_width = self.original_image.shape[:2]

            # 创建原始图像的副本用于绘图
            self.display_image = self.original_image.copy()

            # 转换为灰度图
            self.gray_image = cv2.cvtColor(self.original_image, cv2.COLOR_BGR2GRAY)

            # 检测扫描图像特征
            self._detect_scan_image_characteristics()

            # 根据检测结果选择增强方法
            if self.use_scan_optimization:
                # 使用扫描图像增强
                self.enhanced_image = self._enhance_scanned_image(self.gray_image)
                self.scan_enhanced = self.enhanced_image.copy()
            else:
                # 使用原有增强方法
                clahe = cv2.createCLAHE(clipLimit=2.0, tileGridSize=(8, 8))
                self.enhanced_image = clahe.apply(self.gray_image)

            return True, "图像加载成功"
        except Exception as e:
            return False, f"图像加载失败: {str(e)}"

    def _detect_scan_image_characteristics(self):
        """检测扫描图像特征"""
        try:
            # 计算图像统计特征
            mean_val = np.mean(self.gray_image)
            std_val = np.std(self.gray_image)

            # 计算边缘检测
            edges = cv2.Canny(self.gray_image, 50, 150)
            edge_percentage = np.sum(edges > 0) / (self.gray_image.shape[0] * self.gray_image.shape[1])

            # 计算直方图
            hist = cv2.calcHist([self.gray_image], [0], None, [256], [0, 256])
            hist_peaks = self._check_histogram_peaks(hist)

            # 判断是否为扫描图像
            # 扫描图像通常背景均匀（标准差小），边缘占比低，直方图有明显峰
            is_uniform_background = std_val < 30
            has_low_edge_percentage = edge_percentage < 0.1
            has_clear_peaks = hist_peaks

            if is_uniform_background and has_low_edge_percentage:
                self.scan_params['is_scanned'] = True

                # 检测背景类型（亮/暗）
                self.scan_params['background_type'] = 'light' if mean_val > 128 else 'dark'

                # 估计扫描质量
                hist_smoothness = np.std(hist)
                if hist_smoothness < 100:
                    self.scan_params['scan_quality'] = 'high'
                elif hist_smoothness < 300:
                    self.scan_params['scan_quality'] = 'medium'
                else:
                    self.scan_params['scan_quality'] = 'low'

                print(
                    f"检测到扫描图像: 背景类型={self.scan_params['background_type']}, 质量={self.scan_params['scan_quality']}")

        except Exception as e:
            print(f"扫描图像检测失败: {e}")
            self.scan_params['is_scanned'] = False

    def _check_histogram_peaks(self, hist):
        """检查直方图是否有明显峰"""
        try:
            # 寻找峰值
            hist_flat = hist.flatten()

            # 计算平滑后的直方图
            hist_smooth = np.convolve(hist_flat, np.ones(5) / 5, mode='same')

            # 寻找局部极大值
            peaks = []
            for i in range(1, len(hist_smooth) - 1):
                if hist_smooth[i] > hist_smooth[i - 1] and hist_smooth[i] > hist_smooth[i + 1]:
                    peaks.append(i)

            # 如果有2个或更少的明显峰（黑白图像），可能是扫描图像
            return len(peaks) <= 2
        except:
            return False

    def _enhance_scanned_image(self, gray_image):
        """
        针对扫描图像的简化增强
        扫描图像通常背景均匀，无需复杂的光照校正
        """
        # 轻微对比度增强，避免过度处理
        return self._mild_contrast_enhance(gray_image)

    def _mild_contrast_enhance(self, image):
        """轻微对比度增强，避免过度处理"""
        # 1. 获取图像的最小和最大像素值
        min_val = np.min(image)
        max_val = np.max(image)

        # 2. 线性拉伸到[0, 255]
        if max_val > min_val:
            enhanced = ((image - min_val) * 255.0 / (max_val - min_val)).astype(np.uint8)
        else:
            enhanced = image

        # 3. 轻微锐化（可选，根据扫描质量决定）
        if self.scan_params['scan_quality'] == 'high':
            kernel = np.array([[0, -1, 0],
                               [-1, 5, -1],
                               [0, -1, 0]])
            enhanced = cv2.filter2D(enhanced, -1, kernel)

        return enhanced

    def enable_scan_optimization(self, enable=True):
        """启用或禁用扫描图像优化"""
        self.use_scan_optimization = enable
        if enable and hasattr(self, 'gray_image'):
            # 重新增强图像
            self.enhanced_image = self._enhance_scanned_image(self.gray_image)
            self.scan_enhanced = self.enhanced_image.copy()
        elif hasattr(self, 'gray_image'):
            # 恢复原有增强方法
            clahe = cv2.createCLAHE(clipLimit=2.0, tileGridSize=(8, 8))
            self.enhanced_image = clahe.apply(self.gray_image)

        return self.use_scan_optimization

    def set_scan_background_type(self, bg_type):
        """设置扫描背景类型"""
        if bg_type in ['light', 'dark', 'auto']:
            self.scan_params['background_type'] = bg_type
            if bg_type == 'auto':
                # 自动检测
                mean_val = np.mean(self.gray_image) if hasattr(self, 'gray_image') else 128
                self.scan_params['background_type'] = 'light' if mean_val > 128 else 'dark'
            return True
        return False

    def set_scan_quality(self, quality):
        """设置扫描质量"""
        if quality in ['high', 'medium', 'low', 'auto']:
            self.scan_params['scan_quality'] = quality
            return True
        return False

    def segment_roots(self, method='otsu'):
        """分割根系 - 保留大津法，增加扫描图像优化"""
        try:
            # 如果启用扫描图像优化，使用专用分割方法
            if self.use_scan_optimization and self.scan_params['is_scanned']:
                return self._segment_scanned_roots()

            # 否则使用原大津法
            _, binary = cv2.threshold(
                self.enhanced_image, 0, 255,
                cv2.THRESH_BINARY_INV + cv2.THRESH_OTSU
            )

            # 基本形态学操作
            kernel = np.ones((3, 3), np.uint8)
            binary = cv2.morphologyEx(binary, cv2.MORPH_OPEN, kernel)
            binary = cv2.morphologyEx(binary, cv2.MORPH_CLOSE, kernel)

            self.binary_mask = binary

            # 应用ROI裁剪
            if self.roi_active is not None:
                x1, y1, x2, y2 = [int(v) for v in self.roi_active]
                h, w = self.binary_mask.shape[:2]
                x1, x2 = max(0, x1), min(w, x2)
                y1, y2 = max(0, y1), min(h, y2)
                roi_mask = np.zeros((h, w), dtype=np.uint8)
                roi_mask[y1:y2, x1:x2] = 255
                self.binary_mask = cv2.bitwise_and(self.binary_mask, roi_mask)

            return True, "图像分割完成（使用大津法）"
        except Exception as e:
            return False, f"分割失败: {str(e)}"

    def _segment_scanned_roots(self):
        """针对扫描图像优化的分割方法"""
        try:
            # 扫描图像通常对比度好，使用简单的阈值分割
            # 计算自适应阈值
            mean_val = np.mean(self.enhanced_image)

            if self.scan_params['background_type'] == 'light':
                # 对于白色背景，根系通常较暗
                _, binary = cv2.threshold(
                    self.enhanced_image,
                    mean_val * 0.6,  # 自适应阈值
                    255,
                    cv2.THRESH_BINARY_INV
                )
            else:  # 暗背景
                # 对于黑色背景，根系通常较亮
                _, binary = cv2.threshold(
                    self.enhanced_image,
                    mean_val * 1.4,  # 自适应阈值
                    255,
                    cv2.THRESH_BINARY
                )

            # 简化形态学操作（扫描图像通常干净）
            kernel = np.ones((2, 2), np.uint8)
            binary = cv2.morphologyEx(binary, cv2.MORPH_CLOSE, kernel, iterations=1)
            binary = cv2.morphologyEx(binary, cv2.MORPH_OPEN, kernel, iterations=1)

            self.binary_mask = binary

            # 应用ROI裁剪
            if self.roi_active is not None:
                x1, y1, x2, y2 = [int(v) for v in self.roi_active]
                h, w = self.binary_mask.shape[:2]
                x1, x2 = max(0, x1), min(w, x2)
                y1, y2 = max(0, y1), min(h, y2)
                roi_mask = np.zeros((h, w), dtype=np.uint8)
                roi_mask[y1:y2, x1:x2] = 255
                self.binary_mask = cv2.bitwise_and(self.binary_mask, roi_mask)

            return True, "扫描图像分割完成"

        except Exception as e:
            # 如果失败，回退到原方法
            return False, f"扫描图像分割失败: {str(e)}"

    def filter_non_roots(self, min_length=5, min_area=20, min_aspect_ratio=1.0):
        """
        简化版根系过滤算法 - 只保留三个关键参数
        增加扫描图像优化版本
        """
        try:
            # 如果启用扫描图像优化，使用专用过滤方法
            if self.use_scan_optimization and self.scan_params['is_scanned']:
                return self._filter_non_roots_scanned(min_length, min_area, min_aspect_ratio)

            # 原有过滤算法
            labeled_image = measure.label(self.binary_mask)
            props = measure.regionprops_table(
                labeled_image,
                properties=[
                    'label', 'area', 'major_axis_length', 'minor_axis_length'
                ]
            )

            n_regions = len(props['label'])
            filtered_mask = np.zeros_like(self.binary_mask)
            filtered_count = 0

            # 预计算条件
            major_axis = props['major_axis_length']
            minor_axis = props['minor_axis_length']
            areas = props['area']

            # 避免除零
            minor_axis_safe = np.where(minor_axis == 0, 0.01, minor_axis)
            aspect_ratios = major_axis / minor_axis_safe

            # 1. 面积过滤
            area_condition = areas >= min_area

            # 2. 长度过滤
            length_condition = major_axis >= min_length

            # 3. 纵横比过滤
            aspect_condition = aspect_ratios >= min_aspect_ratio

            # 综合所有条件
            valid_conditions = area_condition & length_condition & aspect_condition
            valid_indices = np.where(valid_conditions)[0]

            # 应用过滤结果
            for idx in valid_indices:
                label = props['label'][idx]
                filtered_mask[labeled_image == label] = 255
                filtered_count += 1

            # 后处理 - 形态学操作连接断裂的根系
            if filtered_count > 0:
                kernel = np.ones((3, 3), np.uint8)
                # 先闭运算填充小孔
                filtered_mask = cv2.morphologyEx(filtered_mask, cv2.MORPH_CLOSE, kernel, iterations=1)
                # 再开运算去除小噪点
                filtered_mask = cv2.morphologyEx(filtered_mask, cv2.MORPH_OPEN, kernel, iterations=1)

            self.filtered_mask = filtered_mask
            self.filtered_count = filtered_count

            # 保存过滤统计信息
            self.filter_stats = {
                'total_regions': n_regions,
                'filtered_regions': filtered_count,
                'removed_regions': n_regions - filtered_count,
                'removal_percentage': ((n_regions - filtered_count) / n_regions * 100) if n_regions > 0 else 0,
                'average_area': np.mean(areas) if len(areas) > 0 else 0,
                'average_aspect_ratio': np.mean(aspect_ratios) if len(aspect_ratios) > 0 else 0
            }

            # 保存被过滤区域的统计信息
            filtered_areas = areas[valid_indices] if len(valid_indices) > 0 else []
            if len(filtered_areas) > 0:
                self.filter_stats.update({
                    'filtered_min_area': np.min(filtered_areas),
                    'filtered_max_area': np.max(filtered_areas),
                    'filtered_avg_area': np.mean(filtered_areas)
                })

            return True, f"过滤完成，保留{filtered_count}个根系对象（过滤掉{n_regions - filtered_count}个）"
        except Exception as e:
            # 如果过滤失败，使用原始掩码
            self.filtered_mask = self.binary_mask.copy()
            labeled = measure.label(self.binary_mask)
            self.filtered_count = np.max(labeled) if np.max(labeled) > 0 else 0
            self.filter_stats = {
                'total_regions': self.filtered_count,
                'filtered_regions': self.filtered_count,
                'removed_regions': 0,
                'removal_percentage': 0.0,
                'error': str(e)
            }
            return False, f"过滤失败，使用原始图像: {str(e)}"

    def _filter_non_roots_scanned(self, min_length=3, min_area=10, min_aspect_ratio=0.8):
        """
        针对扫描图像的过滤优化
        扫描图像中的根系通常更清晰，噪声更少
        """
        try:
            labeled_image = measure.label(self.binary_mask)
            props = measure.regionprops_table(
                labeled_image,
                properties=['label', 'area', 'major_axis_length', 'minor_axis_length']
            )

            n_regions = len(props['label'])
            filtered_mask = np.zeros_like(self.binary_mask)
            filtered_count = 0

            # 扫描图像可以放宽过滤条件
            # 因为根系通常更完整，噪声更少
            for i in range(n_regions):
                area = props['area'][i]
                major_axis = props['major_axis_length'][i]
                minor_axis = props['minor_axis_length'][i]

                # 避免除零
                if minor_axis == 0:
                    aspect_ratio = 0
                else:
                    aspect_ratio = major_axis / minor_axis

                # 扫描图像的过滤条件（更宽松）
                if (area >= min_area and
                        major_axis >= min_length and
                        aspect_ratio >= min_aspect_ratio):
                    label = props['label'][i]
                    filtered_mask[labeled_image == label] = 255
                    filtered_count += 1

            self.filtered_mask = filtered_mask
            self.filtered_count = filtered_count

            # 保存过滤统计
            self.filter_stats = {
                'total_regions': n_regions,
                'filtered_regions': filtered_count,
                'removed_regions': n_regions - filtered_count,
                'removal_percentage': ((n_regions - filtered_count) / n_regions * 100) if n_regions > 0 else 0,
                'average_area': np.mean(props['area']) if len(props['area']) > 0 else 0,
                'scan_optimized': True  # 标记为扫描优化
            }

            return True, f"扫描图像过滤完成，保留{filtered_count}个根系对象"

        except Exception as e:
            # 如果失败，使用原过滤方法
            return self.filter_non_roots(min_length, min_area, min_aspect_ratio)

    def count_roots(self, min_size=50):
        """简化版：只计数根系，不分离个体细节"""
        try:
            if not hasattr(self, 'filtered_mask') or np.sum(self.filtered_mask) == 0:
                self.root_count = 0
                return True, "没有检测到根系"

            # 使用连通域分析计算根系数量
            num_labels, labels, stats, centroids = cv2.connectedComponentsWithStats(
                self.filtered_mask, connectivity=8
            )

            # 统计满足最小尺寸条件的根系
            root_count = 0
            self.connected_components = []

            for i in range(1, num_labels):  # 跳过背景(0)
                area = stats[i, cv2.CC_STAT_AREA]
                if area >= min_size:
                    root_count += 1

                    # 计算根系长度（使用骨架长度）
                    root_mask = (labels == i).astype(np.uint8) * 255
                    root_length = self._calculate_root_length(root_mask)

                    # 计算根系直径
                    root_diameter = self._calculate_root_diameter(area, root_length)

                    # 计算根系体积和表面积
                    root_volume = self._calculate_root_volume(root_length, root_diameter)
                    root_surface = self._calculate_root_surface(root_length, root_diameter)

                    # 保存连通组件信息
                    self.connected_components.append({
                        'id': root_count,
                        'area_pixels': area,
                        'area_mm2': area * self.pixel_to_mm ** 2,
                        'length_pixels': root_length / self.pixel_to_mm,
                        'length_mm': root_length,
                        'diameter_mm': root_diameter,
                        'volume_mm3': root_volume,
                        'surface_mm2': root_surface,
                        'centroid': centroids[i],  # (x, y)坐标
                        'bounding_box': stats[i, :4],  # x, y, width, height
                        'label': i  # 在标签图像中的标签值
                    })

            self.root_count = root_count

            # 创建简单的彩色标注图用于显示
            self._create_simple_color_map(labels, num_labels)

            return True, f"检测到 {root_count} 个根系"

        except Exception as e:
            self.root_count = 0
            return False, f"根系计数失败: {str(e)}"

    def _calculate_root_length(self, root_mask):
        """计算根系长度（骨架长度）"""
        try:
            # 骨架化计算长度
            skeleton = morphology.skeletonize(root_mask > 0)
            skeleton_pixels = np.sum(skeleton)
            return skeleton_pixels * self.pixel_to_mm
        except:
            # 如果骨架化失败，使用面积估算长度
            area_pixels = np.sum(root_mask > 0)
            return np.sqrt(area_pixels) * self.pixel_to_mm

    def _calculate_root_diameter(self, area_pixels, length_mm):
        """计算根系直径"""
        try:
            if length_mm <= 0:
                return 0.0

            # 假设根系为圆柱体，直径 = 面积 / 长度
            area_mm2 = area_pixels * self.pixel_to_mm ** 2
            return area_mm2 / length_mm
        except:
            return 0.0

    def _calculate_root_volume(self, length_mm, diameter_mm):
        """计算根系体积"""
        try:
            if diameter_mm <= 0:
                return 0.0

            # 假设根系为圆柱体，体积 = π * (d/2)² * L
            radius = diameter_mm / 2
            return math.pi * radius * radius * length_mm
        except:
            return 0.0

    def _calculate_root_surface(self, length_mm, diameter_mm):
        """计算根系表面积"""
        try:
            if diameter_mm <= 0:
                return 0.0

            # 假设根系为圆柱体，表面积 = π * d * L
            return math.pi * diameter_mm * length_mm
        except:
            return 0.0

    def _create_simple_color_map(self, labels, num_labels):
        """创建简化的彩色标注图"""
        try:
            if num_labels <= 1:  # 只有背景
                return

            # 创建彩色图像
            height, width = labels.shape
            color_map = np.zeros((height, width, 3), dtype=np.uint8)

            # 为每个根系分配颜色（简化版）
            for i, component in enumerate(self.connected_components, 1):
                # 生成一致的颜色
                hue = (i * 137) % 360
                rgb = colorsys.hsv_to_rgb(hue / 360, 0.8, 1.0)
                color = [int(c * 255) for c in rgb]

                # 将该根系对应的区域着色
                mask = (labels == component['label'])
                color_map[mask] = color

            self.color_map = color_map

        except Exception as e:
            print(f"创建彩色标注图失败: {e}")

    def calculate_root_parameters(self):
        """计算根系参数：比根长、总根表面积、总根体积、总根长、根直径分布"""
        try:
            if not self.connected_components:
                return False, "没有根系数据，请先进行根系计数"

            # 初始化统计变量
            total_length = 0.0
            total_area = 0.0
            total_volume = 0.0
            total_surface = 0.0
            diameters = []

            # 统计所有根系
            for component in self.connected_components:
                total_length += component['length_mm']
                total_area += component['area_mm2']
                total_volume += component['volume_mm3']
                total_surface += component['surface_mm2']
                diameters.append(component['diameter_mm'])

            # 计算平均直径
            avg_diameter = np.mean(diameters) if diameters else 0.0

            # 计算比根长（总根长/总根系面积）
            specific_root_length = total_length / total_area if total_area > 0 else 0.0

            # 根据直径分级并计算体积占比
            diameter_distribution = self._classify_roots_by_diameter(diameters, self.connected_components)

            # 保存参数
            self.root_parameters = {
                'total_length': total_length,
                'total_area': total_area,
                'total_volume': total_volume,
                'total_surface': total_surface,
                'avg_diameter': avg_diameter,
                'specific_root_length': specific_root_length,
                'diameter_distribution': diameter_distribution
            }

            return True, "根系参数计算完成"
        except Exception as e:
            return False, f"根系参数计算失败: {str(e)}"

    def _classify_roots_by_diameter(self, diameters, components):
        """根据根直径对根系进行分级并计算体积占比（使用自定义或默认分级）"""
        try:
            # 初始化统计
            classification = {}
            total_volume = sum(c['volume_mm3'] for c in components)

            for class_name, min_d, max_d in self._get_diameter_classes():
                class_roots = []
                class_volume = 0.0
                class_count = 0

                for i, component in enumerate(components):
                    diameter = component['diameter_mm']
                    if max_d == float('inf'):
                        if diameter >= min_d:
                            in_range = True
                        else:
                            in_range = False
                    else:
                        in_range = (min_d <= diameter < max_d)

                    if in_range:
                        class_roots.append({
                            'id': component['id'],
                            'diameter': diameter,
                            'length': component['length_mm'],
                            'volume': component['volume_mm3']
                        })
                        class_volume += component['volume_mm3']
                        class_count += 1

                # 计算体积占比
                volume_percentage = (class_volume / total_volume * 100) if total_volume > 0 else 0

                classification[class_name] = {
                    'count': class_count,
                    'volume_mm3': round(class_volume, 3),
                    'volume_percentage': round(volume_percentage, 2),
                    'avg_diameter_mm': round(np.mean([r['diameter'] for r in class_roots]), 3) if class_roots else 0,
                    'min_diameter_mm': round(min([r['diameter'] for r in class_roots]), 3) if class_roots else 0,
                    'max_diameter_mm': round(max([r['diameter'] for r in class_roots]), 3) if class_roots else 0
                }

            return classification
        except Exception as e:
            print(f"根系分级失败: {e}")
            return {}

    def calculate_parameters(self):
        """计算根系参数（增强版）- 包含更多详细参数"""
        try:
            # 检查是否有过滤后的掩码
            if not hasattr(self, 'filtered_mask') or np.sum(self.filtered_mask) == 0:
                # 即使没有根系，也初始化所有字段为0或默认值
                self.results = {
                    '图像名称': self.image_name,
                    '分析时间': datetime.now().strftime('%Y-%m-%d %H:%M:%S'),
                    '像素转换系数(mm/像素)': self.pixel_to_mm,
                    '图像宽度(mm)': round(self.image_width * self.pixel_to_mm, 2),
                    '图像高度(mm)': round(self.image_height * self.pixel_to_mm, 2),
                    '根系数量': 0,
                    '总根长(mm)': 0.0,
                    '根系面积(mm²)': 0.0,
                    '图像宽度(像素)': self.image_width,
                    '图像高度(像素)': self.image_height,
                    '最大根系面积(mm²)': 0.0,
                    '最小根系面积(mm²)': 0.0,
                    '平均根系面积(mm²)': 0.0,
                    '面积标准差(mm²)': 0.0,
                    '面积变异系数(%)': 0.0,
                    '最大根系长度(mm)': 0.0,
                    '最小根系长度(mm)': 0.0,
                    '平均根系长度(mm)': 0.0,
                    '长度标准差(mm)': 0.0,
                    '最大根系直径(mm)': 0.0,
                    '最小根系直径(mm)': 0.0,
                    '平均根系直径(mm)': 0.0,
                    '直径标准差(mm)': 0.0,
                    '总根系体积(mm³)': 0.0,
                    '平均根系体积(mm³)': 0.0,
                    '总根系表面积(mm²)': 0.0,
                    '平均根系表面积(mm²)': 0.0,
                    '总根体积(mm³)': 0.0,
                    '总根表面积(mm²)': 0.0,
                    '比根长(mm/mm²)': 0.0,
                    '总根长(累计)(mm)': 0.0,
                    '平均根直径(mm)': 0.0
                }

                # 添加直径分级字段（即使为0也保留）
                for class_name, _, _ in self._get_diameter_classes():
                    self.results[f'{class_name}数量'] = 0
                    self.results[f'{class_name}体积(mm³)'] = 0.0
                    self.results[f'{class_name}体积占比(%)'] = 0.0
                    self.results[f'{class_name}平均直径(mm)'] = 0.0

                return True, "没有检测到根系，所有参数设置为0"

            # 计算总面积
            root_area_pixels = np.sum(self.filtered_mask > 0)
            root_area_mm2 = root_area_pixels * self.pixel_to_mm ** 2

            # 骨架化计算总长度
            binary_for_skeleton = self.filtered_mask > 0
            skeleton = morphology.skeletonize(binary_for_skeleton)
            skeleton_pixels = np.sum(skeleton)
            total_length_pixels = skeleton_pixels
            total_length_mm = total_length_pixels * self.pixel_to_mm

            # 保存整体结果
            self.results = {
                '图像名称': self.image_name,
                '分析时间': datetime.now().strftime('%Y-%m-%d %H:%M:%S'),
                '像素转换系数(mm/像素)': self.pixel_to_mm,
                '图像宽度(mm)': round(self.image_width * self.pixel_to_mm, 2),
                '图像高度(mm)': round(self.image_height * self.pixel_to_mm, 2),
                '根系数量': self.root_count,
                '总根长(mm)': round(total_length_mm, 2),
                '根系面积(mm²)': round(root_area_mm2, 2),
                '图像宽度(像素)': self.filtered_mask.shape[1],
                '图像高度(像素)': self.filtered_mask.shape[0]
            }

            # 如果有根系信息，添加尺寸分布
            if self.connected_components:
                areas = [c['area_mm2'] for c in self.connected_components]
                lengths = [c['length_mm'] for c in self.connected_components]
                diameters = [c['diameter_mm'] for c in self.connected_components]
                volumes = [c['volume_mm3'] for c in self.connected_components]
                surfaces = [c['surface_mm2'] for c in self.connected_components]

                self.results.update({
                    '最大根系面积(mm²)': round(max(areas), 2) if areas else 0.0,
                    '最小根系面积(mm²)': round(min(areas), 2) if areas else 0.0,
                    '平均根系面积(mm²)': round(np.mean(areas), 2) if areas else 0.0,
                    '面积标准差(mm²)': round(np.std(areas), 2) if areas else 0.0,
                    '面积变异系数(%)': round((np.std(areas) / np.mean(areas) * 100) if np.mean(areas) > 0 else 0, 2),
                    '最大根系长度(mm)': round(max(lengths), 2) if lengths else 0.0,
                    '最小根系长度(mm)': round(min(lengths), 2) if lengths else 0.0,
                    '平均根系长度(mm)': round(np.mean(lengths), 2) if lengths else 0.0,
                    '长度标准差(mm)': round(np.std(lengths), 2) if lengths else 0.0,
                    '最大根系直径(mm)': round(max(diameters), 3) if diameters else 0.0,
                    '最小根系直径(mm)': round(min(diameters), 3) if diameters else 0.0,
                    '平均根系直径(mm)': round(np.mean(diameters), 3) if diameters else 0.0,
                    '直径标准差(mm)': round(np.std(diameters), 3) if diameters else 0.0,
                    '总根系体积(mm³)': round(sum(volumes), 2) if volumes else 0.0,
                    '平均根系体积(mm³)': round(np.mean(volumes), 2) if volumes else 0.0,
                    '总根系表面积(mm²)': round(sum(surfaces), 2) if surfaces else 0.0,
                    '平均根系表面积(mm²)': round(np.mean(surfaces), 2) if surfaces else 0.0
                })
            else:
                # 即使没有根系组件，也添加这些字段为0
                self.results.update({
                    '最大根系面积(mm²)': 0.0,
                    '最小根系面积(mm²)': 0.0,
                    '平均根系面积(mm²)': 0.0,
                    '面积标准差(mm²)': 0.0,
                    '面积变异系数(%)': 0.0,
                    '最大根系长度(mm)': 0.0,
                    '最小根系长度(mm)': 0.0,
                    '平均根系长度(mm)': 0.0,
                    '长度标准差(mm)': 0.0,
                    '最大根系直径(mm)': 0.0,
                    '最小根系直径(mm)': 0.0,
                    '平均根系直径(mm)': 0.0,
                    '直径标准差(mm)': 0.0,
                    '总根系体积(mm³)': 0.0,
                    '平均根系体积(mm³)': 0.0,
                    '总根系表面积(mm²)': 0.0,
                    '平均根系表面积(mm²)': 0.0
                })

            # 添加根系参数
            if hasattr(self, 'root_parameters') and self.root_parameters:
                self.results.update({
                    '总根体积(mm³)': round(self.root_parameters['total_volume'], 2),
                    '总根表面积(mm²)': round(self.root_parameters['total_surface'], 2),
                    '比根长(mm/mm²)': round(self.root_parameters['specific_root_length'], 4),
                    '总根长(累计)(mm)': round(self.root_parameters['total_length'], 2),
                    '平均根直径(mm)': round(self.root_parameters['avg_diameter'], 3)
                })

                # 添加直径分级信息
                if 'diameter_distribution' in self.root_parameters:
                    dist = self.root_parameters['diameter_distribution']
                    for class_name, class_data in dist.items():
                        if class_data['count'] > 0:
                            self.results[f'{class_name}数量'] = class_data['count']
                            self.results[f'{class_name}体积(mm³)'] = round(class_data['volume_mm3'], 2)
                            self.results[f'{class_name}体积占比(%)'] = round(class_data['volume_percentage'], 2)
                            self.results[f'{class_name}平均直径(mm)'] = round(class_data['avg_diameter_mm'], 3)
            else:
                # 如果没有根系参数，添加默认值
                self.results.update({
                    '总根体积(mm³)': 0.0,
                    '总根表面积(mm²)': 0.0,
                    '比根长(mm/mm²)': 0.0,
                    '总根长(累计)(mm)': 0.0,
                    '平均根直径(mm)': 0.0
                })

            # 确保所有直径分级字段都存在，即使为0
            for class_name, _, _ in self._get_diameter_classes():
                if f'{class_name}数量' not in self.results:
                    self.results[f'{class_name}数量'] = 0
                if f'{class_name}体积(mm³)' not in self.results:
                    self.results[f'{class_name}体积(mm³)'] = 0.0
                if f'{class_name}体积占比(%)' not in self.results:
                    self.results[f'{class_name}体积占比(%)'] = 0.0
                if f'{class_name}平均直径(mm)' not in self.results:
                    self.results[f'{class_name}平均直径(mm)'] = 0.0

            return True, "参数计算完成"
        except Exception as e:
            return False, f"参数计算失败: {str(e)}"

    def set_scale_from_measurement(self, measured_length_mm, pixel_length):
        """通过已知测量设置比例尺"""
        try:
            if pixel_length <= 0:
                return False, "像素长度必须大于0"

            self.pixel_to_mm = measured_length_mm / pixel_length
            return True, f"比例设置成功: {self.pixel_to_mm:.4f} mm/像素"
        except Exception as e:
            return False, f"设置比例失败: {str(e)}"

    def set_scale_from_dimensions(self, width_mm, height_mm):
        """通过图像尺寸设置比例尺"""
        try:
            if width_mm <= 0 or height_mm <= 0:
                return False, "尺寸必须大于0"

            # 使用平均比例
            width_scale = width_mm / self.image_width
            height_scale = height_mm / self.image_height
            self.pixel_to_mm = (width_scale + height_scale) / 2

            return True, f"比例设置成功: {self.pixel_to_mm:.4f} mm/像素"
        except Exception as e:
            return False, f"设置比例失败: {str(e)}"

    def _draw_text_pil(self, image, text, position, font_size=18, color=(255, 255, 255)):
        """使用PIL绘制中文文本（替代cv2.putText，支持CJK字符）"""
        img_pil = Image.fromarray(cv2.cvtColor(image, cv2.COLOR_BGR2RGB))
        draw = ImageDraw.Draw(img_pil)
        font = ImageFont.truetype("C:/Windows/Fonts/simhei.ttf", font_size)
        draw.text(position, text, font=font, fill=color)
        return cv2.cvtColor(np.array(img_pil), cv2.COLOR_RGB2BGR)

    def _get_text_size_pil(self, text, font_size=18):
        """获取PIL文本尺寸"""
        font = ImageFont.truetype("C:/Windows/Fonts/simhei.ttf", font_size)
        bbox = font.getbbox(text)
        return bbox[2] - bbox[0], bbox[3] - bbox[1]

    def add_scale_bar(self, image, length_mm=10, position=(50, 50), color=(255, 255, 255), thickness=2):
        """在图像上添加比例尺"""
        try:
            # 计算比例尺的像素长度
            bar_length_pixels = int(length_mm / self.pixel_to_mm)

            # 绘制比例尺
            x, y = position
            cv2.rectangle(image,
                          (x, y - thickness - 5),
                          (x + bar_length_pixels, y + 15),
                          (0, 0, 0), -1)

            cv2.line(image,
                     (x, y),
                     (x + bar_length_pixels, y),
                     color, thickness)

            # 使用PIL绘制文本（支持中文）
            label = f"{length_mm} mm"
            text_w, text_h = self._get_text_size_pil(label, font_size=14)
            text_x = x + (bar_length_pixels - text_w) // 2
            image = self._draw_text_pil(image, label, (text_x, y + 15), font_size=14, color=color)

            return image
        except Exception as e:
            print(f"添加比例尺失败: {e}")
            return image

    def generate_detailed_report_image(self, output_path, show_scale=True):
        """生成详细分析报告图像"""
        try:
            fig = plt.figure(figsize=(18, 12))
            fig.suptitle(f'根系详细分析报告 - {self.image_name}', fontsize=18, fontweight='bold')

            # 创建子图布局
            gs = fig.add_gridspec(3, 4, hspace=0.3, wspace=0.3)

            # 1. 原始图像
            ax1 = fig.add_subplot(gs[0, 0])
            ax1.imshow(cv2.cvtColor(self.original_image, cv2.COLOR_BGR2RGB))
            ax1.set_title('原始图像', fontsize=12, fontweight='bold')
            ax1.axis('off')

            # 添加图像尺寸信息
            info_text = f'尺寸: {self.image_width}×{self.image_height} 像素\n'
            info_text += f'实际: {self.image_width * self.pixel_to_mm:.1f}×{self.image_height * self.pixel_to_mm:.1f} mm'
            ax1.text(0.02, 0.98, info_text, transform=ax1.transAxes,
                     fontsize=8, color='white',
                     verticalalignment='top',
                     bbox=dict(boxstyle='round', facecolor='black', alpha=0.5))

            # 2. 增强图像
            ax2 = fig.add_subplot(gs[0, 1])
            # 根据是否为扫描图像选择显示方式
            if self.use_scan_optimization and hasattr(self, 'scan_enhanced'):
                ax2.imshow(self.scan_enhanced, cmap='gray')
                ax2.set_title('扫描图像增强', fontsize=12, fontweight='bold')
            else:
                ax2.imshow(self.enhanced_image, cmap='gray')
                ax2.set_title('对比度增强', fontsize=12, fontweight='bold')
            ax2.axis('off')

            # 3. 分割结果
            ax3 = fig.add_subplot(gs[0, 2])
            if hasattr(self, 'binary_mask'):
                ax3.imshow(self.binary_mask, cmap='gray')
                method_title = '扫描图像分割' if self.use_scan_optimization else '分割结果（大津法）'
                ax3.set_title(method_title, fontsize=12, fontweight='bold')
                ax3.axis('off')
                ax3.text(0.02, 0.98, f'区域数: {self.filtered_count}',
                         transform=ax3.transAxes, fontsize=8, color='white',
                         verticalalignment='top',
                         bbox=dict(boxstyle='round', facecolor='black', alpha=0.5))

            # 4. 过滤结果
            ax4 = fig.add_subplot(gs[0, 3])
            if hasattr(self, 'filtered_mask'):
                ax4.imshow(self.filtered_mask, cmap='gray')
                filter_title = '扫描图像过滤' if self.use_scan_optimization else '过滤结果'
                ax4.set_title(filter_title, fontsize=12, fontweight='bold')
                ax4.axis('off')
                filter_info = f"过滤后: {self.filtered_count}个"
                if self.use_scan_optimization:
                    filter_info += " (扫描优化)"
                ax4.text(0.02, 0.98, filter_info,
                         transform=ax4.transAxes, fontsize=8, color='white',
                         verticalalignment='top',
                         bbox=dict(boxstyle='round', facecolor='blue', alpha=0.5))

            # 5. 根系计数结果
            ax5 = fig.add_subplot(gs[1, :2])
            if hasattr(self, 'color_map'):
                ax5.imshow(self.color_map)
                ax5.set_title(f'根系计数 ({self.root_count}个)', fontsize=12, fontweight='bold')
                ax5.axis('off')

            # 6. 结果叠加
            ax6 = fig.add_subplot(gs[1, 2:])
            if hasattr(self, 'filtered_mask'):
                overlay = self.original_image.copy()
                overlay[self.filtered_mask > 0] = [0, 255, 0]

                # 添加比例尺
                if show_scale:
                    overlay = self.add_scale_bar(overlay, length_mm=self.scale_bar_length_mm)

                ax6.imshow(cv2.cvtColor(overlay, cv2.COLOR_BGR2RGB))
                ax6.set_title('检测结果叠加', fontsize=12, fontweight='bold')
                ax6.axis('off')

                # 添加参数摘要
                if self.results:
                    summary = f"根系数量: {self.results.get('根系数量', 0)}\n"
                    summary += f"总根长: {self.results.get('总根长(mm)', 0):.1f} mm\n"
                    summary += f"根系面积: {self.results.get('根系面积(mm²)', 0):.1f} mm²\n"
                    summary += f"总根体积: {self.results.get('总根体积(mm³)', 0):.1f} mm³"
                    ax6.text(0.02, 0.98, summary, transform=ax6.transAxes,
                             fontsize=8, color='white',
                             verticalalignment='top',
                             bbox=dict(boxstyle='round', facecolor='green', alpha=0.7))

            # 7. 直径分布柱状图
            ax7 = fig.add_subplot(gs[2, 0])
            if hasattr(self, 'root_parameters') and 'diameter_distribution' in self.root_parameters:
                dist = self.root_parameters['diameter_distribution']
                classes = list(dist.keys())
                volumes = [dist[c]['volume_mm3'] for c in classes]
                percentages = [dist[c]['volume_percentage'] for c in classes]

                color_cycle = ['#ff9999', '#66b3ff', '#99ff99', '#ffcc99', '#c2c2f0',
                               '#ffb3e6', '#c2f0c2', '#ffccb3', '#b3b3ff', '#ffb366']
                colors = list(itertools.islice(itertools.cycle(color_cycle), len(classes)))
                bars = ax7.bar(classes, volumes, color=colors)
                ax7.set_title('根系直径分级体积分布', fontsize=12, fontweight='bold')
                ax7.set_ylabel('体积 (mm³)', fontsize=10)
                ax7.tick_params(axis='x', rotation=45)

                # 在柱状图上添加百分比标签
                for bar, percentage in zip(bars, percentages):
                    height = bar.get_height()
                    ax7.text(bar.get_x() + bar.get_width() / 2., height + max(volumes) * 0.01,
                             f'{percentage}%', ha='center', va='bottom', fontsize=9)

            # 8. 根系参数汇总表
            ax8 = fig.add_subplot(gs[2, 1:])
            ax8.axis('off')

            if hasattr(self, 'root_parameters') and self.root_parameters:
                # 创建参数表格
                params_data = [
                    ['参数', '数值', '单位'],
                    ['总根长', f"{self.root_parameters['total_length']:.1f}", 'mm'],
                    ['根系面积', f"{self.root_parameters['total_area']:.1f}", 'mm²'],
                    ['总根体积', f"{self.root_parameters['total_volume']:.1f}", 'mm³'],
                    ['总根表面积', f"{self.root_parameters['total_surface']:.1f}", 'mm²'],
                    ['平均根直径', f"{self.root_parameters['avg_diameter']:.3f}", 'mm'],
                    ['比根长', f"{self.root_parameters['specific_root_length']:.4f}", 'mm/mm²']
                ]

                table = ax8.table(cellText=params_data, loc='center', cellLoc='center')
                table.auto_set_font_size(False)
                table.set_fontsize(9)
                table.scale(1, 1.5)
                ax8.set_title('根系参数汇总', fontsize=12, fontweight='bold')

            plt.tight_layout(rect=[0, 0, 1, 0.96])
            plt.savefig(output_path, dpi=200, bbox_inches='tight', facecolor='white')
            plt.close()

            return True, "详细报告图像生成成功"
        except Exception as e:
            return False, f"报告图像生成失败: {str(e)}"

    def export_overlay_image(self, output_path, show_scale=True):
        """导出叠加结果图"""
        try:
            if not hasattr(self, 'filtered_mask'):
                return False, "没有可导出的结果"

            # 创建叠加图像
            overlay = self.original_image.copy()

            # 绘制检测到的根系
            overlay[self.filtered_mask > 0] = [0, 255, 0]

            # 添加比例尺
            if show_scale:
                overlay = self.add_scale_bar(overlay, length_mm=self.scale_bar_length_mm)

            # 使用PIL绘制中文文本
            scan_info = " [扫描优化]" if self.use_scan_optimization else ""
            info_text = f"{self.image_name} | 根系数量: {self.root_count}{scan_info} | {datetime.now().strftime('%Y-%m-%d %H:%M')}"
            overlay = self._draw_text_pil(overlay, info_text, (10, 10), font_size=18)

            # 添加参数信息
            if hasattr(self, 'root_parameters'):
                param_text = f"总根长: {self.root_parameters['total_length']:.1f}mm | "
                param_text += f"体积: {self.root_parameters['total_volume']:.1f}mm³"
                overlay = self._draw_text_pil(overlay, param_text, (10, 38), font_size=16)

            # 保存图像
            cv2.imwrite(output_path, overlay)
            return True, "叠加图像导出成功"
        except Exception as e:
            return False, f"叠加图像导出失败: {str(e)}"

    def save_results_csv(self, output_path):
        """保存结果为CSV - 增强版，输出所有根系参数"""
        try:
            # 定义所有可能的字段，确保即使值为0也保留
            all_fields = [
                '图像名称', '分析时间', '像素转换系数(mm/像素)', '图像宽度(mm)', '图像高度(mm)',
                '根系数量', '总根长(mm)', '根系面积(mm²)', '图像宽度(像素)', '图像高度(像素)',
                '最大根系面积(mm²)', '最小根系面积(mm²)', '平均根系面积(mm²)', '面积标准差(mm²)', '面积变异系数(%)',
                '最大根系长度(mm)', '最小根系长度(mm)', '平均根系长度(mm)', '长度标准差(mm)',
                '最大根系直径(mm)', '最小根系直径(mm)', '平均根系直径(mm)', '直径标准差(mm)',
                '总根系体积(mm³)', '平均根系体积(mm³)', '总根系表面积(mm²)', '平均根系表面积(mm²)',
                '总根体积(mm³)', '总根表面积(mm²)', '比根长(mm/mm²)', '总根长(累计)(mm)', '平均根直径(mm)',
            ]
            # 动态添加直径分级字段
            for class_name, _, _ in self._get_diameter_classes():
                keys = self._get_class_suffix_keys(class_name)
                all_fields.extend([keys['count'], keys['volume'], keys['volume_pct'], keys['avg_diam']])
            all_fields.extend(['分析类型', '扫描优化'])

            # 准备数据 - 确保所有字段都存在，即使值为0
            data = {}
            for field in all_fields:
                if field in self.results:
                    data[field] = self.results[field]
                elif field == '分析类型':
                    data[field] = '总体'
                elif field == '扫描优化':
                    data[field] = '是' if self.use_scan_optimization else '否'
                else:
                    # 对于数值字段，设置为0
                    if '数量' in field or '体积' in field or '面积' in field or '长度' in field or '直径' in field or '比根长' in field:
                        data[field] = 0.0
                    elif '占比' in field:
                        data[field] = 0.0
                    else:
                        data[field] = ''

            # 如果文件存在，追加模式；否则创建新文件
            file_exists = os.path.isfile(output_path)

            with open(output_path, 'a', newline='', encoding='utf-8-sig') as f:
                writer = csv.DictWriter(f, fieldnames=all_fields)
                if not file_exists:
                    writer.writeheader()
                writer.writerow(data)

            # 保存根系分级详细数据
            if hasattr(self, 'root_parameters') and 'diameter_distribution' in self.root_parameters:
                detail_path = output_path.replace('.csv', '_分级详细.csv')
                with open(detail_path, 'w', newline='', encoding='utf-8-sig') as f:
                    writer = csv.writer(f)
                    writer.writerow(['根系直径分级详细报告'])
                    writer.writerow(['图像名称', self.image_name])
                    writer.writerow(['分析时间', datetime.now().strftime('%Y-%m-%d %H:%M:%S')])
                    writer.writerow(['扫描优化', '是' if self.use_scan_optimization else '否'])
                    writer.writerow([])

                    writer.writerow(['直径分级', '数量', '体积(mm³)', '体积占比(%)',
                                     '平均直径(mm)', '最小直径(mm)', '最大直径(mm)'])

                    dist = self.root_parameters['diameter_distribution']
                    for class_name, _, _ in self._get_diameter_classes():
                        class_data = dist.get(class_name, {
                            'count': 0,
                            'volume_mm3': 0.0,
                            'volume_percentage': 0.0,
                            'avg_diameter_mm': 0.0,
                            'min_diameter_mm': 0.0,
                            'max_diameter_mm': 0.0
                        })
                        writer.writerow([
                            class_name,
                            class_data['count'],
                            round(class_data['volume_mm3'], 3),
                            round(class_data['volume_percentage'], 2),
                            round(class_data['avg_diameter_mm'], 3),
                            round(class_data['min_diameter_mm'], 3),
                            round(class_data['max_diameter_mm'], 3)
                        ])

                    # 添加汇总
                    writer.writerow([])
                    writer.writerow(['参数汇总'])
                    writer.writerow(['总根系数量', self.root_count])
                    writer.writerow(['总根体积(mm³)', round(self.root_parameters.get('total_volume', 0), 2)])
                    writer.writerow(['总根长(mm)', round(self.root_parameters.get('total_length', 0), 2)])
                    writer.writerow(['总根表面积(mm²)', round(self.root_parameters.get('total_surface', 0), 2)])
                    writer.writerow(['平均根直径(mm)', round(self.root_parameters.get('avg_diameter', 0), 3)])
                    writer.writerow(['根系面积(mm²)', round(self.root_parameters.get('total_area', 0), 2)])
                    writer.writerow(['比根长(mm/mm²)', round(self.root_parameters.get('specific_root_length', 0), 4)])

                    # 添加尺寸分布信息
                    writer.writerow([])
                    writer.writerow(['尺寸分布统计'])
                    writer.writerow(['最大根系面积(mm²)', self.results.get('最大根系面积(mm²)', 0)])
                    writer.writerow(['最小根系面积(mm²)', self.results.get('最小根系面积(mm²)', 0)])
                    writer.writerow(['平均根系面积(mm²)', self.results.get('平均根系面积(mm²)', 0)])
                    writer.writerow(['面积标准差(mm²)', self.results.get('面积标准差(mm²)', 0)])
                    writer.writerow(['面积变异系数(%)', self.results.get('面积变异系数(%)', 0)])
                    writer.writerow(['最大根系长度(mm)', self.results.get('最大根系长度(mm)', 0)])
                    writer.writerow(['最小根系长度(mm)', self.results.get('最小根系长度(mm)', 0)])
                    writer.writerow(['平均根系长度(mm)', self.results.get('平均根系长度(mm)', 0)])
                    writer.writerow(['长度标准差(mm)', self.results.get('长度标准差(mm)', 0)])
                    writer.writerow(['最大根系直径(mm)', self.results.get('最大根系直径(mm)', 0)])
                    writer.writerow(['最小根系直径(mm)', self.results.get('最小根系直径(mm)', 0)])
                    writer.writerow(['直径标准差(mm)', self.results.get('直径标准差(mm)', 0)])
                    writer.writerow(['总根系体积(mm³)', self.results.get('总根系体积(mm³)', 0)])
                    writer.writerow(['平均根系体积(mm³)', self.results.get('平均根系体积(mm³)', 0)])
                    writer.writerow(['总根系表面积(mm²)', self.results.get('总根系表面积(mm²)', 0)])
                    writer.writerow(['平均根系表面积(mm²)', self.results.get('平均根系表面积(mm²)', 0)])

            return True, "CSV保存成功"
        except Exception as e:
            return False, f"CSV保存失败: {str(e)}"

    def save_results_json(self, output_path):
        """保存结果为JSON"""
        try:
            # 读取现有数据或创建新列表
            if os.path.exists(output_path):
                with open(output_path, 'r', encoding='utf-8') as f:
                    data = json.load(f)
            else:
                data = []

            # 创建完整结果
            complete_result = {
                '总体结果': self.results,
                '根系参数': self.root_parameters,
                '分析时间': datetime.now().strftime('%Y-%m-%d %H:%M:%S'),
                '图像信息': {
                    '文件名': self.image_name,
                    '尺寸_像素': f"{self.image_width}x{self.image_height}",
                    '尺寸_mm': f"{self.image_width * self.pixel_to_mm:.1f}x{self.image_height * self.pixel_to_mm:.1f}",
                    '像素转换系数': self.pixel_to_mm
                },
                '扫描优化': self.use_scan_optimization,
                '扫描参数': self.scan_params if self.use_scan_optimization else None
            }

            # 添加新结果
            data.append(complete_result)

            # 保存
            with open(output_path, 'w', encoding='utf-8') as f:
                json.dump(data, f, indent=2, ensure_ascii=False)
            return True, "JSON保存成功"
        except Exception as e:
            return False, f"JSON保存失败: {str(e)}"

    # 静态方法用于并行处理
    @staticmethod
    def analyze_single_image_static(params):
        """
        静态方法：分析单个图像（用于多进程）
        参数params是一个包含所有必要参数的字典
        返回: (成功标志, 结果字典, 错误信息)
        """
        try:
            # 记录内存使用情况
            process = psutil.Process(os.getpid())
            initial_memory = process.memory_info().rss / 1024 / 1024  # MB

            image_path = params['image_path']
            pixel_to_mm = params['pixel_to_mm']
            seg_method = params['seg_method']
            min_length = params['min_length']
            min_area = params['min_area']
            min_aspect_ratio = params['min_aspect_ratio']
            min_root_size = params['min_root_size']
            output_dir = params.get('output_dir', os.path.dirname(image_path))
            use_scan_optimization = params.get('use_scan_optimization', False)
            scan_background_type = params.get('scan_background_type', 'auto')
            scan_quality = params.get('scan_quality', 'auto')
            roi_active = params.get('roi_active', None)

            # 创建分析器实例
            analyzer = RootSystemAnalyzer(pixel_to_mm)
            analyzer.roi_active = roi_active
            if params.get('diameter_classes') is not None:
                analyzer.diameter_classes = params['diameter_classes']

            # 设置扫描优化参数
            if use_scan_optimization:
                analyzer.enable_scan_optimization(True)
                analyzer.set_scan_background_type(scan_background_type)
                analyzer.set_scan_quality(scan_quality)

            # 加载图像
            success, message = analyzer.load_image(image_path)
            if not success:
                return False, {}, message

            # 分割 - 仅使用大津法或扫描优化
            success, message = analyzer.segment_roots(method='otsu')
            if not success:
                return False, {}, message

            # 过滤
            success, message = analyzer.filter_non_roots(
                min_length=min_length,
                min_area=min_area,
                min_aspect_ratio=min_aspect_ratio
            )
            if not success:
                return False, {}, message

            # 计数根系
            success, message = analyzer.count_roots(min_size=min_root_size)
            if not success:
                return False, {}, message

            # 计算根系参数
            success, message = analyzer.calculate_root_parameters()
            if not success:
                return False, {}, message

            # 计算所有参数
            success, message = analyzer.calculate_parameters()
            if not success:
                return False, {}, message

            # 准备结果
            result = {
                'success': True,
                'analyzer': analyzer,
                'image_name': analyzer.image_name,
                'results': analyzer.results.copy(),
                'root_parameters': analyzer.root_parameters.copy(),
                'filter_stats': analyzer.filter_stats.copy(),
                'root_count': analyzer.root_count,
                'total_length': analyzer.root_parameters.get('total_length', 0),
                'total_area': analyzer.root_parameters.get('total_area', 0),
                'total_volume': analyzer.root_parameters.get('total_volume', 0),
                'use_scan_optimization': use_scan_optimization
            }

            # 为每个图像生成叠加图 - 关键修复
            try:
                # 确保输出目录存在
                os.makedirs(output_dir, exist_ok=True)

                # 生成叠加图
                base_name = os.path.splitext(os.path.basename(image_path))[0]
                timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
                overlay_path = os.path.join(output_dir, f"{base_name}_结果叠加_{timestamp}.png")

                # 检查是否有过滤后的掩码
                if hasattr(analyzer, 'filtered_mask') and np.sum(analyzer.filtered_mask) > 0:
                    # 生成叠加图像
                    overlay = analyzer.original_image.copy()
                    overlay[analyzer.filtered_mask > 0] = [0, 255, 0]

                    # 使用PIL绘制中文文本
                    scan_info = " [扫描优化]" if use_scan_optimization else ""
                    info_text = f"{analyzer.image_name} | 根系数量: {analyzer.root_count}{scan_info} | {datetime.now().strftime('%Y-%m-%d %H:%M')}"
                    overlay = analyzer._draw_text_pil(overlay, info_text, (10, 10), font_size=18)

                    # 保存图像
                    cv2.imwrite(overlay_path, overlay)
                    result['overlay_path'] = overlay_path
                    print(f"已生成叠加图: {overlay_path}")
                else:
                    print(f"没有检测到根系，跳过叠加图生成: {image_path}")
                    result['overlay_path'] = None
            except Exception as e:
                print(f"生成叠加图失败: {e}")
                result['overlay_path'] = None

            # 清理分析器中的大对象以节省内存
            for attr in ['original_image', 'enhanced_image', 'binary_mask',
                         'filtered_mask', 'color_map', 'gray_image', 'display_image']:
                if hasattr(analyzer, attr):
                    setattr(analyzer, attr, None)

            # 强制垃圾回收
            gc.collect()

            # 记录最终内存使用
            final_memory = process.memory_info().rss / 1024 / 1024  # MB
            memory_used = final_memory - initial_memory
            print(f"进程 {os.getpid()} 内存使用: {initial_memory:.1f}MB -> {final_memory:.1f}MB (Δ{memory_used:.1f}MB)")

            return True, result, "分析成功"

        except Exception as e:
            return False, {}, f"分析失败: {str(e)}"

